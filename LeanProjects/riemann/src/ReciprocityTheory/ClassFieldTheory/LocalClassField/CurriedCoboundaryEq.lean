import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.IsTwoCocycleCoboundary

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Coh.CohomologyFunctoriality₂ ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cur (M : TRep R G) (x : M.coch.X 2) (g h : G) : M.V := x.1 ![g, h]

theorem cur_sub (M : TRep R G) (x x' : M.coch.X 2) (g h : G) :
    cur M (x - x') g h = cur M x g h - cur M x' g h := rfl

theorem isTwoCocycle_curried (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) : IsTwoCocycle M.rho (cur M x) := by
  intro g h k
  have := congrFun (LowDeg.dn_eq_zero M hx) ![g, h, k]
  rw [LowDeg.dn_two_apply] at this
  exact this

theorem ext2 (M : TRep R G) {x x' : M.coch.X 2} (h : ∀ g h, cur M x g h = cur M x' g h) : x = x' := by
  refine Subtype.ext (funext fun v => ?_)
  have hv : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [hv]; exact h _ _

theorem continuous_cur (M : TRep R G) (x : M.coch.X 2) {X : Type*} [TopologicalSpace X] {f h : X → G}
    (hf : Continuous f) (hh : Continuous h) : Continuous fun t => cur M x (f t) (h t) := by
  refine (show Continuous x.1 from x.2).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact hf
  · exact hh

def mk1 (M : TRep R G) (y : G → M.V) (hy : Continuous y) : M.coch.X 1 :=
  ⟨fun v => y (v 0), hy.comp (continuous_apply 0)⟩

theorem curried_coboundary_eq (M : TRep R G) (y : G → M.V) (hy : Continuous y) (g h : G) :
    cur M (M.coch.d 1 (mk1 M y hy)) g h = D1 M.rho y g h := oneDifferential_val M _ g h

theorem d_sub_d (M : TRep R G) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0) (w : M.coch.X 1) :
    M.coch.d 2 (x - M.coch.d 1 w) = 0 := by
  rw [map_sub, hx, M.coch.dd, sub_zero]

theorem continuous_comp_rep (U : Subgroup G) (hU : IsOpen (U : Set G)) {Y : Type*} [TopologicalSpace Y]
    (e : G → Y) : Continuous fun g => e (rep U g) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x := by
    refine (hU.preimage (continuous_mul_const _)).mem_nhds ?_
    simp [U.one_mem]
  refine (continuousAt_const (y := e (rep U x))).congr ?_
  filter_upwards [hn] with y hy
  have : y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x := by simp
  rw [this, rep_mul]

variable (M : TRep R G) (N : Subgroup G)

theorem retr_mul_rep (g : G) : (retr N g : G) * rep N g = g := by simp [retr_spec]

theorem retr_mul' (n : G) (hn : n ∈ N) (g : G) : (retr N (n * g) : G) = n * retr N g :=
  congrArg Subtype.val (retr_mul N ⟨n, hn⟩ g)

theorem rep_mul' (n : G) (hn : n ∈ N) (g : G) : rep N (n * g) = rep N g := rep_mul N ⟨n, hn⟩ g

theorem continuous_retr' (hN : IsOpen (N : Set G)) : Continuous fun g => (retr N g : G) :=
  continuous_subtype_val.comp (continuous_retr N hN)

theorem norm0 (hN : IsOpen (N : Set G)) (x : M.coch.X 2)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ m ∈ N, cur M (x - M.coch.d 1 w) n m = 0 := by
  obtain ⟨y, hy⟩ := (memB _).1 hres
  have hc : Continuous fun g : G => (y.1 (e1 (retr N g * (retr N 1)⁻¹)) : M.V) :=
    (show Continuous y.1 from y.2).comp
      (continuous_pi fun _ => (continuous_retr N hN).mul continuous_const)
  have hval : ∀ n : N, retr N (n : G) * (retr N 1)⁻¹ = n := fun n => by
    have := retr_mul N n 1
    rw [mul_one] at this
    rw [this, mul_inv_cancel_right]
  obtain ⟨Y, hYc, hYv⟩ : ∃ Y : G → M.V, Continuous Y ∧ ∀ n : N, Y n = y.1 (e1 n) :=
    ⟨fun g => y.1 (e1 (retr N g * (retr N 1)⁻¹)), hc, fun n => by
      show y.1 (e1 (retr N (n : G) * (retr N 1)⁻¹)) = _
      rw [hval]⟩
  refine ⟨mk1 M Y hYc, fun n hn m hm => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  have h1 := oneDifferential_val (M.resSub N) y ⟨n, hn⟩ ⟨m, hm⟩
  rw [hy] at h1
  have h2 : ((Pair.res M N.subtype continuous_subtype_val).hom.f 2 x).1 ![⟨n, hn⟩, ⟨m, hm⟩] = cur M x n m := by
    refine congrArg x.1 (funext fun i => ?_)
    fin_cases i <;> rfl
  rw [h2] at h1
  rw [h1]
  simp only [D1]
  have e1' : Y n = y.1 (e1 ⟨n, hn⟩) := hYv ⟨n, hn⟩
  have e2' : Y m = y.1 (e1 ⟨m, hm⟩) := hYv ⟨m, hm⟩
  have e3' : Y (n * m) = y.1 (e1 (⟨n, hn⟩ * ⟨m, hm⟩)) := hYv (⟨n, hn⟩ * ⟨m, hm⟩)
  rw [e1', e2', e3']
  exact sub_self _

theorem normA (hN : IsOpen (N : Set G)) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ m ∈ N, cur M x n m = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 := by
  have hc : Continuous fun g : G => - cur M x (retr N g) (rep N g) :=
    (continuous_cur M x (continuous_retr' N hN) (continuous_rep N hN)).neg
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq]
  exact stepA (isTwoCocycle_curried M x hx) (retr_mul_rep N) (fun g => (retr N g).2) (retr_mul' N) (rep_mul' N) h0 n hn g

theorem normB [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0) (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  have hC := isTwoCocycle_curried M x hx
  have hex : ∀ g : G, ∃ e : M.V, (g ∈ N → e = 0) ∧
      ∀ n ∈ N, cur M x g (g⁻¹ * n * g) = e - M.rho n e := by
    intro g
    by_cases hg : g ∈ N
    · exact ⟨0, fun _ => rfl, fun n _ => by rw [h0 g hg, map_zero, sub_zero]⟩
    · let θ : (M.resSub N).coch.X 1 := ⟨fun v => cur M x g (g⁻¹ * (v 0 : G) * g),
        continuous_cur M x continuous_const
          ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply 0))).mul continuous_const)⟩
      have hθ : (M.resSub N).coch.d 1 θ = 0 := by
        rw [wach_d1_eq_zero_iff]
        intro a b
        show cur M x g (g⁻¹ * ((a * b : N) : G) * g) =
          cur M x g (g⁻¹ * (a : G) * g) + M.rho (a : G) (cur M x g (g⁻¹ * (b : G) * g))
        have e1 : g⁻¹ * ((a * b : N) : G) * g = (g⁻¹ * (a : G) * g) * (g⁻¹ * (b : G) * g) := by
          rw [Subgroup.coe_mul]; group
        rw [e1, theta_mul hC h0 g _ (Subgroup.Normal.conj_mem' ‹_› _ a.2 g)]
        congr 3
        group
      have hz : (Submodule.Quotient.mk ⟨θ, (memZ _).2 hθ⟩ : (M.resSub N).H 1) = 0 := Subsingleton.elim _ _
      rw [mk_eq_zero_iff, mem_oneCoboundaries_iff] at hz
      obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ a : N, cur M x g (g⁻¹ * (a : G) * g) = M.rho (a : G) m - m := hz
      refine ⟨-m, fun h => absurd h hg, fun n hn => ?_⟩
      have h' : cur M x g (g⁻¹ * n * g) = M.rho n m - m := hm ⟨n, hn⟩
      rw [h', map_neg]; abel
  choose e he0 he using hex
  have hc : Continuous fun g : G => M.rho (retr N g : G) (e (rep N g)) :=
    M.cont.comp (f := fun g : G => ((retr N g : G), e (rep N g)))
      ((continuous_retr' N hN).prodMk (continuous_comp_rep N hN e))
  refine ⟨mk1 M _ hc, fun n hn g => ?_⟩
  rw [cur_sub, curried_coboundary_eq, cur_sub, curried_coboundary_eq]
  exact stepB hC (retr_mul_rep N) (fun g => (retr N g).2) (retr_mul' N) (rep_mul' N) h0 e he0 he n hn g

theorem norm_all [N.Normal] (hN : IsOpen (N : Set G)) (h1 : Subsingleton ((M.resSub N).H 1)) (x : M.coch.X 2)
    (hx : M.coch.d 2 x = 0)
    (hres : (Pair.res M N.subtype continuous_subtype_val).hom.f 2 x ∈ (M.resSub N).coch.B 2) :
    ∃ w : M.coch.X 1, ∀ n ∈ N, ∀ g, cur M (x - M.coch.d 1 w) n g = 0 ∧ cur M (x - M.coch.d 1 w) g n = 0 := by
  obtain ⟨w0, h0⟩ := norm0 M N hN x hres
  obtain ⟨w1, hA⟩ := normA M N hN _ (d_sub_d M x hx w0) h0
  obtain ⟨w2, hB⟩ := normB M N hN h1 _ (d_sub_d M _ (d_sub_d M x hx w0) w1) hA
  refine ⟨w0 + w1 + w2, ?_⟩
  have : x - M.coch.d 1 (w0 + w1 + w2) = x - M.coch.d 1 w0 - M.coch.d 1 w1 - M.coch.d 1 w2 := by
    rw [map_add, map_add]; abel
  rw [this]
  exact hB

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
